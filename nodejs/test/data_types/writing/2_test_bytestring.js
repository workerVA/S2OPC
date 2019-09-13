const sopc_client = require('../../../lib/sopc_client');
const assert = require('assert');

const default_endpoint = "opc.tcp://localhost:4841";
const default_security_policy = sopc_client.security_policy.None_URI;
const default_security_mode = sopc_client.security_mode.None;
const default_user_security_policy_id = "anonymous";

var connectionId = 0;

function connect() {
    var status = true;
    if (status) {
        status = sopc_client.initialize("./log/", sopc_client.log_level.Error);
    }

    if (status) {
        var endpoint = default_endpoint;
        var securityCfg = new sopc_client.SecurityCfg(default_security_policy,
            default_security_mode,
            default_user_security_policy_id);
        connectionId = sopc_client.connect(endpoint, securityCfg);
        status = (connectionId > 0);
    }
    return status;
}

function disconnect(connectionId){
    sopc_client.disconnect(connectionId);
    sopc_client.finalize();
}

describe("Write ByteString type", function() {
    describe("ByteString type", function () {
        before(function(done) {
            connect();
            done();
        });
        it("Every result shall be OK", function (done) {
            var variant = new sopc_client.Variant()
                .setValue(15, 0, "12345abcdef");
            var data_value = new sopc_client.DataValue()
                                            .setValue(variant);
            var write_value_string = new sopc_client.WriteValue()
                .setNodeId("ns=1;i=1005")
                .setValue(data_value);
            var write_values = [write_value_string];

            var resultStatusCodes;
            var status;
            [status, resultStatusCodes] = sopc_client.write(connectionId,
                write_values);
            assert.equal(status, 0, `Status is ${status}`);
            assert.equal(resultStatusCodes.length, 1);
            for (var elt of resultStatusCodes) {
                assert.equal(elt, 0, `Status is ${elt}`);
            }
            done();
        });
        after(function(done) {
            disconnect(connectionId);
            done();
        });
    });
});
