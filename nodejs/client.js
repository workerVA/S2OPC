//const util = require('util');
const sopc_client = require('./sopc_client');

const default_endpoint = "opc.tcp://localhost:4841";
const default_security_policy = sopc_client.security_policy.None_URI;
const default_security_mode = sopc_client.security_mode.None;
const default_user_security_policy_id = "anonymous";

const yargs = require('yargs');

const argv = yargs
    .usage("$0 -e <endpointURL> <NODE_ID> [<NODE_ID> ...]")
    .option('endpoint', {
        alias: 'e',
        description: 'URL of the endpoint to connect to',
        type: 'string',
    })

    .help()
    .alias('help', 'h')
    .argv;

var status = argv._.length > 0;

if(status){
    status = sopc_client.initialize("./log/", sopc_client.log_level.Debug);
}else{
    throw "Missing node id(s). See '--help' option"
}

var callback = function(connectionId, dataId, dataValue) {
    console.log("connectionId: ", connectionId);
    console.log("dataId: ", dataId);
    console.log("value quality: ", dataValue.quality);
    console.log("value source TS: ", dataValue.src_ts);
    console.log("value server TS: ", dataValue.srv_ts);
    console.log("value: ", dataValue.value);
}

var connectionId = 0;
if(status){
    var endpoint = (argv.endpoint ? argv.endpoint : default_endpoint);
    var securityCfg = new sopc_client.SecurityCfg(default_security_policy,
                                              default_security_mode,
                                              default_user_security_policy_id);
    var connectionRes = sopc_client.connect(endpoint, securityCfg);
    status = connectionRes[0];
    connectionId = connectionRes[1];
    console.log("Connection status:", status ? "SUCCESS" : "FAILED");
    console.log("Connection Id:", connectionId);
}

if (status)
{
    status = sopc_client.createSubscription(connectionId, callback);
    console.log("Subscription status:", status ? "SUCCESS" : "FAILED");
}

if(status){
    argv._.forEach((v) => {
        if(typeof v !== 'string'){
            throw `'${v}' is not a string`
        }
    });
    status = sopc_client.addMonitoredItems(connectionId, argv._);
    console.log("Adding monitored items status:", status ? "SUCCESS" : "FAILED");
} else {
    status = false;
}

function disconnect(connectionId){
    sopc_client.disconnect(connectionId);
    sopc_client.finalize();
}

if (status)
{
    setTimeout(disconnect, 1000000, connectionId);
}
else
{
    disconnect(connectionId);
}

