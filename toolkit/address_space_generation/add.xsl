<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
version="2.0" xmlns:ua="http://opcfoundation.org/UA/2011/03/UANodeSet.xsd"  xmlns:uax="http://opcfoundation.org/UA/2008/02/Types.xsd"  xmlns:xsd="http://www.w3.org/2001/XMLSchema" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xmlns:sys="http://www.systerel.fr" >
    <xsl:output method="text"  encoding="UTF-8" />

<!--

Généralité.

Analyse là https://trac.aix.systerel.fr/ingopcs/ticket/198

Ordre des noeuds
================
A chaque noeud on fait correspondre un entier le désignant et qui correspond au type B.

Cependant pour optimiser l'implantation mémoire, il faut numéroter les noeuds en les regroupants par classe et suivant l'ordre des classes dans le tableau suivant 'classes'.

Les noeuds sont finalement recopiés dans une variable : 'ua_nodes'.
Les templates de productions sont ensuites appliqués à partir de cette variable : mode 'copy'.

Alias
======
Le reference type d'une reference peut être aliasé.
Par exemple, l'alias suivant est défini :
     <Alias Alias="HasComponent">i=47</Alias>

Et une référence peut être donnée à l'aide de cet alias par exemple :
     <Reference IsForward="false" ReferenceType="HasComponent">ns=261;s=Objec ...

Lors de la recopie des noeuds, les templates de recopie permettent de remplacer les alias par leur valeur.


NodeId
=======
Pour chaque nodeId une variable est créée ayant pour nom 'nodeid_{indice}'.
Les tableaux sont ensuite des tableaux de pointeur sur ces variables.
La correspondance entre les nodesId et le nom de la variable correspondant est codée en créant des noeuds de la forme :
    <n id="la chaine donnant le node id" vn="nodeid_{position()}"/>
Ces noeuds sont contenus dans la variable nodeid_var_names.


Indice à 1
==============
La valeur à l'indice zéro d'un tableau, zéro étant utilisé pour le codage des valeurs indet, est non significative.
Les valeurs significatives commence à l'indice 1.

Fonction
========
Le codage des fonctions consiste à produire un tableau des valeurs sont crées dans l'ordre des noeuds.
Soit la valeur est directe, soit il y a une résolution par exemple dans le cas de la fonction NodeId où la valeur est un pointeur sur la variable correspondante.

Relation
==========
Les relations sont codées par trois tableaux :
Un tableau qui est constitué de la liste des listes des valeurs des éléments.
Par exemple pour la relation
    - {1|-> 2, 1|->3, 3|->2}

Le tableau est :
    - {0, 2, 3, 2}

Deux tableau qui donnent l'indice de début, et de fin, des éléments associés à l'élément.

Dans le cas précédent on a
    - deb = {0, 1, 1, 3}
    - fin = {0, 2, 0, 3}

A noté que pour un élément qui n'a pas d'image, l'indice de fin est strictement plus petit que l'indice de début.

-->

<%
classes = ('View', 'Object', 'Variable', 'VariableType', 'ObjectType', 'ReferenceType', 'DataType', 'Method')
%>

<!-- variable contenant les alias -->
<xsl:variable name="alias" select="//ua:Alias"/>

<!-- variable contenant une recopie des noeuds à traiter afin de les ordonner. -->
<xsl:variable name="ua_nodes">
    <xsl:apply-templates select="${ '|'.join(['*/ua:UA' + s for s  in classes])}" mode="copy">
        <xsl:sort select="sys:ord_class(.)"/>
    </xsl:apply-templates>
</xsl:variable>

<!-- Table d'association entre la chaine donnant un node id et le nom de la variable -->
<xsl:variable name="nodeid_var_name">
    <xsl:for-each select="distinct-values($ua_nodes//@NodeId|$ua_nodes//ua:Reference/text()|$ua_nodes//ua:Reference/@ReferenceType)">
        <n id="{.}" vn="nodeid_{position()}"/>
    </xsl:for-each>
</xsl:variable>

<!-- Variable contenant les noeuds de type variable et variabletype -->
<xsl:variable name="var_vartype" select="$ua_nodes/ua:UAVariable|$ua_nodes/ua:UAVariableType"/>

<xsl:template match="/">
/*
 *  Copyright (C) 2017 Systerel and others.
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as
 *  published by the Free Software Foundation, either version 3 of the
 *  License, or (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see &lt;http://www.gnu.org/licenses/>.
 */

#include "add.h"

#include &lt;stdio.h>
#include &lt;stdbool.h>

#include "sopc_builtintypes.h"
#include "sopc_types.h"
#include "sopc_base_types.h"

% for i in range(1, 9):
#define NB_${i} <xsl:value-of select="count(//ua:UA${classes[i-1]})"/><xsl:text>    /* ${classes[i-1]} */</xsl:text>
% endfor

#define NB (${' + '.join( [ 'NB_%d' % i for i in range(1,9)])})

#define toSOPC_String(s) ((SOPC_Byte*)s)

#define DEFAULT_VARIANT  {SOPC_Null_Id, SOPC_VariantArrayType_SingleValue,{0}}

<!-- Create variables for each node id -->
<xsl:for-each select="$nodeid_var_name/*">
static SOPC_NodeId <xsl:value-of select="@vn"/> = <xsl:apply-templates select="@id" mode="nodeId"/>;<xsl:text/>
static SOPC_ExpandedNodeId ex_<xsl:value-of select="@vn"/> = {<xsl:apply-templates select="@id" mode="nodeId"/>, {0,0, NULL}, 0};<xsl:text/>
</xsl:for-each>

<!-- Avoid unused variable warning -->
void* avoid_unused_nodes_var[] = {<xsl:for-each select="$nodeid_var_name/*">&amp;<xsl:value-of select="@vn"/>,
&amp;ex_<xsl:value-of select="@vn"/>,</xsl:for-each>};

<!-- BrowseName -->
static SOPC_QualifiedName BrowseName[NB + 1] = {{0, {0, 0, NULL}}
<xsl:apply-templates select = "$ua_nodes/*/@BrowseName" mode="qName"/>
};

<!-- Description, DisplayName-->

% for s in ['Description', 'DisplayName']:
static SOPC_LocalizedText ${s}[] = {{{0, 0, NULL}, {0, 0, NULL}}
<xsl:apply-templates select = "$ua_nodes/*/ua:${s}" mode="localized_text"/>
};
static int ${s}_begin[] = {0, <xsl:value-of select = "for $n in $ua_nodes/* return count($n/preceding-sibling::*/ua:${s}) + 1" separator=", "/>};
static int ${s}_end[] = {-1, <xsl:value-of select = "for $n in $ua_nodes/* return count($n/preceding-sibling::*/ua:${s}) +  count($n/ua:${s})" separator=", "/>};
% endfor


<!-- Reference -->
static int reference_begin[] = {0, <xsl:value-of select = "for $n in $ua_nodes/* return count($n/preceding-sibling::*/ua:References/*) + 1" separator=", "/>};
static int reference_end[] = {-1,&#10;<xsl:value-of select = "for $n in $ua_nodes/* return concat(count($n/preceding-sibling::*/ua:References/*), '+',  count($n/ua:References/*), ' /* ', $n/@NodeId, ' */')" separator=",&#10;"/>};
static SOPC_NodeId* reference_type[] = {NULL,  <xsl:value-of select="for $n in $ua_nodes/*/ua:References/* return concat('&amp;', $nodeid_var_name/*[@id = $n/@ReferenceType]/@vn)" separator=", "/>};
static SOPC_ExpandedNodeId* reference_target[] = {NULL, <xsl:value-of select="for $n in $ua_nodes/*/ua:References/* return concat('&amp;ex_', $nodeid_var_name/*[@id = $n/text()]/@vn)" separator=", "/>};
static bool reference_isForward[]={false, <xsl:value-of select="for $n in $ua_nodes/*/ua:References/* return if ($n/@IsForward = 'false') then 'false' else 'true' " separator=", "/>};

<!-- NodeId -->
static SOPC_NodeId* NodeId[NB+1] = {NULL,&#10;<xsl:value-of select="for $n in $ua_nodes/* return concat('&amp;', $nodeid_var_name/*[@id = $n/@NodeId]/@vn)" separator=",&#10;"/>};


<!-- NodeClass -->
static OpcUa_NodeClass NodeClass[NB+1] = {OpcUa_NodeClass_Unspecified,
    <xsl:value-of select="for $n in $ua_nodes/* return sys:get_enum_value($n)" separator=", "/>
};

<!-- Value -->
SOPC_Variant Value[NB_3+NB_4+1] = {DEFAULT_VARIANT<xsl:apply-templates select="$var_vartype" mode="value"/>};

<!-- StatusCode -->
static SOPC_StatusCode status_code[] = {STATUS_NOK, <xsl:value-of select = "for $n in $var_vartype return if ($n/ua:Value) then 'STATUS_OK' else 'STATUS_NOK'" separator=", "/>};

<!-- Access level -->
static SOPC_SByte AccessLevel[] = {0, <xsl:value-of select = "for $n in $ua_nodes/ua:UAVariable return if ($n/@AccessLevel) then $n/@AccessLevel else 1" separator=", "/>};

SOPC_AddressSpace addressSpace = {
    .nbVariables = NB_3,
    .nbVariableTypes = NB_4,
    .nbObjectTypes = NB_5,
    .nbReferenceTypes = NB_6,
    .nbDataTypes = NB_7,
    .nbMethods = NB_8,
    .nbObjects = NB_2,
    .nbViews = NB_1,
    .nbNodesTotal = NB,

    .browseNameArray = BrowseName,
    .descriptionIdxArray_begin = Description_begin,
    .descriptionIdxArray_end = Description_end,
    .descriptionArray = Description,
    .displayNameIdxArray_begin = DisplayName_begin,
    .displayNameIdxArray_end = DisplayName_end,
    .displayNameArray = DisplayName,
    .nodeClassArray = NodeClass,
    .nodeIdArray = NodeId,
    .referenceIdxArray_begin = reference_begin,
    .referenceIdxArray_end = reference_end,
    .referenceTypeArray = reference_type,
    .referenceTargetArray = reference_target,
    .referenceIsForwardArray = reference_isForward,
    .valueArray = Value,
    .valueStatusArray = status_code,
    .accessLevelArray = AccessLevel,
};
</xsl:template>

<!-- Create variant for each variable -->

<xsl:template match="ua:UAVariable[ua:Value]|ua:UAVariableType[ua:Value]" mode="value"><xsl:apply-templates select="ua:Value/*" mode="value"/></xsl:template>
<xsl:template match="ua:UAVariable[not(ua:Value)]|ua:UAVariableType[not(ua:Value)]" mode="value">, DEFAULT_VARIANT</xsl:template>

<xsl:template match="uax:Boolean" mode="value">,{SOPC_Boolean_Id, SOPC_VariantArrayType_SingleValue, {.Boolean=<xsl:value-of select="."/>}}</xsl:template>
<xsl:template match="uax:SByte" mode="value">,{SOPC_SByte_Id, SOPC_VariantArrayType_SingleValue, {.SByte=<xsl:value-of select="."/>}}</xsl:template>
<xsl:template match="uax:Byte" mode="value">,{SOPC_Byte_Id, SOPC_VariantArrayType_SingleValue, {.Byte=<xsl:value-of select="."/>}}</xsl:template>
<xsl:template match="uax:Int16" mode="value">,{SOPC_Int16_Id, SOPC_VariantArrayType_SingleValue, {.Int16=<xsl:value-of select="."/>}}</xsl:template>
<xsl:template match="uax:Uint16" mode="value">,{SOPC_UInt16_Id, SOPC_VariantArrayType_SingleValue, {.Uint16=<xsl:value-of select="."/>}}</xsl:template>
<xsl:template match="uax:Int32" mode="value">,{SOPC_Int32_Id, SOPC_VariantArrayType_SingleValue, {.Int32=<xsl:value-of select="."/>}}</xsl:template>
<xsl:template match="uax:UInt32" mode="value">,{SOPC_UInt32_Id, SOPC_VariantArrayType_SingleValue, {.Uint32=<xsl:value-of select="."/>}}</xsl:template>
<xsl:template match="uax:Int64" mode="value">,{SOPC_Int64_Id, SOPC_VariantArrayType_SingleValue, {.Int64=<xsl:value-of select="."/>}}</xsl:template>
<xsl:template match="uax:UInt64" mode="value">,{SOPC_UInt64_Id, SOPC_VariantArrayType_SingleValue, {.Uint64=<xsl:value-of select="."/>}}</xsl:template>
<xsl:template match="uax:Float" mode="value">,{SOPC_Float_Id, SOPC_VariantArrayType_SingleValue, {.Floatv=<xsl:value-of select="."/>}}</xsl:template>
<xsl:template match="uax:Double" mode="value">,{SOPC_Double_Id, SOPC_VariantArrayType_SingleValue, {.Doublev=<xsl:value-of select="."/>}}</xsl:template>
<xsl:template match="uax:String" mode="value"><xsl:variable name="st" select="translate(.,'&quot;','')"/>,{SOPC_String_Id, SOPC_VariantArrayType_SingleValue, {.String=${write_string("$st")}}}</xsl:template>
<xsl:template match="uax:BString" mode="value"><xsl:variable name="st" select="translate(.,'&quot;','')"/>,{SOPC_ByteString_Id, SOPC_VariantArrayType_SingleValue, {.Bstring=${write_string("$st")}}}</xsl:template>
<xsl:template match="uax:XmlElt" mode="value"><xsl:variable name="st" select="translate(.,'&quot;','')"/>,{SOPC_XmlElement_Id, SOPC_VariantArrayType_SingleValue, {.XmlElt=${write_string("$st")}}}</xsl:template>
<xsl:template match="uax:NodeId" mode="value">,{SOPC_NodeId_Id, SOPC_VariantArrayType_SingleValue, {.NodeId=<xsl:value-of select="."/>}}</xsl:template>
<xsl:template match="uax:Status" mode="value">,{SOPC_StatusCode_Id, SOPC_VariantArrayType_SingleValue, {.Status=<xsl:value-of select="."/>}}</xsl:template>

<xsl:template match="*" mode="value">
<xsl:message terminate="yes"> unknown type <xsl:value-of select="local-name(.)"/>
</xsl:message>
</xsl:template>

<!-- generation of node id -->

<xsl:template match="@*" mode="nodeId">
    <xsl:variable name="NodeId" select="."/>
    <xsl:analyze-string select="$NodeId" regex="(ns=\d+;)?(i=\d+|s=.+)">
        <xsl:matching-substring>
        <xsl:variable name="nsIndex" select="if (regex-group(1)) then substring-after(substring-before(regex-group(1),';'),'=') else 0"/>
        <xsl:variable name="ident" select="regex-group(2)"/>{<xsl:choose>
            <xsl:when test="starts-with($ident, 'i')">IdentifierType_Numeric, <xsl:value-of select="$nsIndex"/>, .Data.Numeric = <xsl:value-of select="substring-after($ident,'=')"/></xsl:when>
            <xsl:when test="starts-with($ident, 's')">IdentifierType_String, <xsl:value-of select="$nsIndex"/>, .Data.String = ${write_string("substring-after($ident,'=')")}</xsl:when>
            <xsl:when test="starts-with($ident, 'g')">IdentifierType_Guid, <xsl:value-of select="$nsIndex"/>, <xsl:value-of select="substring-after($ident,'=')"/></xsl:when>
            <xsl:when test="starts-with($ident, 'b')">IdentifierType_ByteString,  <xsl:value-of select="$nsIndex"/>, <xsl:value-of select="substring-after($ident,'=')"/></xsl:when>
            <xsl:otherwise>
                <xsl:message terminate="yes">Unknown identifier type : '<xsl:value-of select="$ident"/>'.</xsl:message>
            </xsl:otherwise>
        </xsl:choose>
        </xsl:matching-substring>
        <xsl:non-matching-substring>
            <xsl:message  terminate="yes">'<xsl:value-of select="$NodeId"/>' invalid node id</xsl:message>
        </xsl:non-matching-substring>
    </xsl:analyze-string>}<xsl:text/>
</xsl:template>

<xsl:template match="@*" mode="qName">
    <xsl:variable name="bn" select="."/>
    <xsl:variable name="pos" select="position()"/>
    <xsl:variable name="NodeId" select="../@NodeId"/>
    <xsl:analyze-string select="$bn" regex="(\d*):(.*)">
        <xsl:matching-substring>
${print_value(',{%s,{%s,1,toSOPC_String("%s")}}/* %s*/',"regex-group(1)", "string-length(regex-group(2))", "regex-group(2)", "$NodeId")}<xsl:text>
</xsl:text>
        </xsl:matching-substring>
        <xsl:non-matching-substring>
            <xsl:message><xsl:value-of select="$bn"/> invalid qualified string format</xsl:message>
        </xsl:non-matching-substring>
    </xsl:analyze-string>
</xsl:template>

<xsl:template match="*" mode="localized_text">, {${write_string("@Locale")},${write_string("./text()")}}
</xsl:template>

<xsl:template name="write-string">
    <xsl:param name="value"/>${print_value('{%s,1,toSOPC_String("%s")}',"string-length($value)","$value")}
</xsl:template>

<!-- templates de recopie des noeuds -->
<xsl:template match="@ReferenceType" mode="copy">
    <xsl:variable name="type" select="."/>
    <xsl:attribute name="ReferenceType"><xsl:value-of select="$alias[@Alias = $type]"/></xsl:attribute>
</xsl:template>

<xsl:template match="@* | node()" mode="copy">
    <xsl:copy>
        <xsl:apply-templates select="@* | node()" mode="copy"/>
    </xsl:copy>
</xsl:template>

<!-- génération de deux fonction sur le domaine des classes de noeud:
La première 'ord_class' associe à une classe un entier permettant d'ordonner les noeuds par class.
La deuxième 'get_enum_value' retourne l'énuméré C correspondant à une classe. -->
% for (n, f, type) in [('ord_class', lambda x: x, 'integer'), ('get_enum_value', lambda x : 'OpcUa_NodeClass_'+ classes[x-1], 'string')]:
  <xsl:function name="sys:${n}" as="xsd:${type}">
    <xsl:param name="e"/>
    <xsl:variable name='ln' select="local-name($e)"/>
    <xsl:choose>
%   for i in range(1, 9):
    <xsl:when test="$ln='UA${classes[i-1]}'">${f(i)}</xsl:when>
%   endfor
    <xsl:otherwise>
        <xsl:message terminate="yes">Unknown class : '<xsl:value-of select="$ln"/>'.</xsl:message>
    </xsl:otherwise>
    </xsl:choose>
  </xsl:function>
% endfor

<%def name="write_string(value)"><xsl:call-template name="write-string"><xsl:with-param name="value" select="${value}"/></xsl:call-template></%def>

<%def name="print_value(patt, *args)">
    <%doc>
    Function that apply the given template string to the
    result of the XPath queries and returns an output formatted string.
    @patt str: a format string
    @args str: a set of XPath expressions
    </%doc>
${("<xsl:text>"+patt+"</xsl:text>") % tuple(map(lambda x : '</xsl:text><xsl:value-of select="%s"/><xsl:text>' % x, args))}</%def>
</xsl:stylesheet>
