const sopc_client = require('../../../lib/sopc_client');
const test_helper = require('../../helpers/connection');
const assert = require('assert');

describe("Write String type", function() {
    describe("String type", function () {
        let connectionId = 0;
        before(function(done) {
            connectionId = test_helper.connect();
            done();
        });
        it("Every result shall be OK", function (done) {
            let variant = new sopc_client.Variant()
                .setValue(12, 0, "TestTestTEST@test");
            let data_value = new sopc_client.DataValue()
                                            .setValue(variant);
            let write_value_string = new sopc_client.WriteValue()
                .setNodeId("ns=1;i=1004")
                .setValue(data_value);
            let write_values = [write_value_string];

            let resultStatusCodes;
            let status;
            [status, resultStatusCodes] = sopc_client.write(connectionId,
                write_values);
            assert.equal(status, 0, `Status is ${status}`);
            assert.equal(resultStatusCodes.length, 1);
            for (let elt of resultStatusCodes) {
                assert.equal(elt, 0, `Status is ${elt}`);
            }
            done();
        });
        after(function(done) {
            test_helper.disconnect(connectionId);
            done();
        });
    });
});
