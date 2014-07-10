define(["exports"],function(exports) {
  exports["_==_"] = {};
  exports["Vec"] = {};
  exports["ℕ"] = {};
  exports["with-98"] = function (x0) {
      return function (x1) {
        return function (x2) {
          return function (x3) {
            return function (x4) {
              return function (x5) {
                return exports["Vec"]["Cons"](x0)(x5)(exports["_<*>_"]("*")("*")(x0)(exports["vmap"](x2)("*")(x0)(exports["Vec"]["Cons"](x1))(exports["tail"](x0)(x2)(x3)))(exports["transpose"](x0)(x1)(x2)(exports["vmap"]("*")("*")(x1)(exports["tail"](x0)(x2))(x4))));
              };
            };
          };
        };
      };
    };
  exports["append"] = function (x0) {
      return function (x1) {
        return function (x2) {
          return function (x3) {
            return x3({
              "Cons": function (x4, x5, x6) {
                return function (x7) {
                  return exports["Vec"]["Cons"]((x4 + x2))(x5)(exports["append"](x0)(x4)(x2)(x6)(x7));
                };
              },
              "Nil": function () {
                return function (x4) {
                  return x4;
                };
              }
            });
          };
        };
      };
    };
  exports["sum"] = function (x0) {
      return function (x1) {
        return x1({
          "Cons": function (x2, x3, x4) {
            return (x3 + exports["sum"](x2)(x4));
          },
          "Nil": function () {
            return 0;
          }
        });
      };
    };
  exports["Vec"]["Cons"] = function (x0) {
      return function (x1) {
        return function (x2) {
          return function (x3) {
            return x3["Cons"](x0, x1, x2);
          };
        };
      };
    };
  exports["ℕ"]["suc"] = function (x0) {
      return (x0 + 1);
    };
  exports["Matrix"] = function (x0) {
      return function (x1) {
        return function (x2) {
          return "*";
        };
      };
    };
  exports["_*_"] = function (x0) {
      return function (x1) {
        return (x0 * x1);
      };
    };
  exports["tail"] = function (x0) {
      return function (x1) {
        return function (x2) {
          return x2({
            "Cons": function (x3, x4, x5) {
              return x5;
            },
            "Nil": function () {
              return undefined;
            }
          });
        };
      };
    };
  exports["Vec"]["Nil"] = function (x0) {
      return x0["Nil"]();
    };
  exports["idMatrix"] = function (x0) {
      return x0({
        "suc": function (x1) {
          return exports["Vec"]["Cons"](x1)(exports["Vec"]["Cons"](x1)((0 + 1))(exports["pure"](x1)("*")(x1)))(exports["vmap"]("*")("*")(x1)(exports["Vec"]["Cons"](x1)(0))(exports["idMatrix"](x1)));
        },
        "zero": function () {
          return exports["Vec"]["Nil"];
        }
      });
    };
  exports["vmap"] = function (x0) {
      return function (x1) {
        return function (x2) {
          return function (x3) {
            return function (x4) {
              return x4({
                "Cons": function (x5, x6, x7) {
                  return exports["Vec"]["Cons"](x5)(x3(x6))(exports["vmap"](x0)(x1)(x5)(x3)(x7));
                },
                "Nil": function () {
                  return exports["Vec"]["Nil"];
                }
              });
            };
          };
        };
      };
    };
  exports["pure"] = function (x0) {
      return x0({
        "suc": function (x1) {
          return function (x2) {
            return function (x3) {
              return exports["Vec"]["Cons"](x1)(x3)(exports["pure"](x1)(x2)(x3));
            };
          };
        },
        "zero": function () {
          return function (x1) {
            return function (x2) {
              return exports["Vec"]["Nil"];
            };
          };
        }
      });
    };
  exports["madd"] = function (x0) {
      return function (x1) {
        return function (x2) {
          return function (x3) {
            return exports["_<*>_"]("*")("*")(x1)(exports["vmap"]("*")("*")(x1)(function (x4) {
              return exports["_<*>_"]("*")("*")(x0)(exports["vmap"]("*")("*")(x0)(function (x5) {
                return function (x6) {
                  return (x5 + x6);
                };
              })(x4));
            })(x2))(x3);
          };
        };
      };
    };
  exports["_+_"] = function (x0) {
      return function (x1) {
        return (x0 + x1);
      };
    };
  exports["_==_"]["Refl"] = function (x0) {
      return x0["Refl"]();
    };
  exports["head"] = function (x0) {
      return function (x1) {
        return function (x2) {
          return x2({
            "Cons": function (x3, x4, x5) {
              return x4;
            },
            "Nil": function () {
              return undefined;
            }
          });
        };
      };
    };
  exports["transpose"] = function (x0) {
      return x0({
        "suc": function (x1) {
          return function (x2) {
            return x2({
              "suc": function (x3) {
                return function (x4) {
                  return function (x5) {
                    return x5({
                      "Cons": function (x6, x7, x8) {
                        return exports["with-98"](x1)(x3)(x4)(x7)(x8)(exports["vmap"]("*")(x4)((x3 + 1))(exports["head"](x4)(x1))(exports["Vec"]["Cons"](x3)(x7)(x8)));
                      },
                      "Nil": function () {
                        return undefined;
                      }
                    });
                  };
                };
              },
              "zero": function () {
                return function (x3) {
                  return function (x4) {
                    return exports["pure"]((x1 + 1))("*")(exports["Vec"]["Nil"]);
                  };
                };
              }
            });
          };
        },
        "zero": function () {
          return function (x1) {
            return x1({
              "suc": function (x2) {
                return function (x3) {
                  return function (x4) {
                    return exports["Vec"]["Nil"];
                  };
                };
              },
              "zero": function () {
                return function (x2) {
                  return function (x3) {
                    return exports["Vec"]["Nil"];
                  };
                };
              }
            });
          };
        }
      });
    };
  exports["_<*>_"] = function (x0) {
      return function (x1) {
        return function (x2) {
          return function (x3) {
            return x3({
              "Cons": function (x4, x5, x6) {
                return function (x7) {
                  return x7({
                    "Cons": function (x8, x9, x10) {
                      return exports["Vec"]["Cons"](x4)(x5(x9))(exports["_<*>_"](x0)(x1)(x4)(x6)(x10));
                    },
                    "Nil": function () {
                      return undefined;
                    }
                  });
                };
              },
              "Nil": function () {
                return function (x4) {
                  return exports["Vec"]["Nil"];
                };
              }
            });
          };
        };
      };
    };
  exports["ℕ"]["zero"] = 0;
  exports["t1"] = (0 + 1);
  exports["t2"] = (exports["t1"] + 1);
  exports["t3"] = (exports["t2"] + 1);
  exports["t4"] = (exports["t3"] + 1);
  exports["t5"] = (exports["t4"] + 1);
  exports["t10"] = (exports["t5"] + exports["t5"]);
  exports["t11"] = (exports["t10"] + 1);
  exports["t12"] = (exports["t11"] + 1);
  exports["t13"] = (exports["t12"] + 1);
  exports["t20"] = (exports["t10"] + exports["t10"]);
  exports["t30"] = (exports["t20"] + exports["t10"]);
  exports["t40"] = (exports["t30"] + exports["t10"]);
  exports["t50"] = (exports["t40"] + exports["t10"]);
  exports["t200"] = (exports["t50"] + exports["t50"]);
  exports["t234"] = (exports["t200"] + (exports["t30"] + exports["t4"]));
  exports["t400"] = (exports["t200"] + exports["t200"]);
  exports["t800"] = (exports["t400"] + exports["t400"]);
  exports["t100"] = (exports["t50"] + exports["t50"]);
  exports["t543"] = (exports["t400"] + (exports["t100"] + (exports["t40"] + exports["t3"])));
  exports["t23412"] = (((exports["t100"] * exports["t10"]) * (exports["t20"] + exports["t3"])) + (exports["t400"] + exports["t12"]));
  exports["t35413"] = (((exports["t100"] * exports["t10"]) * (exports["t30"] + exports["t5"])) + (exports["t400"] + exports["t13"]));
  exports["t54"] = (exports["t50"] + exports["t4"]);
  exports["t345"] = (exports["t200"] + (exports["t100"] + (exports["t40"] + exports["t5"])));
  exports["_137@12434453"] = {};
  exports["_137@12434453"]["m"] = exports["Vec"]["Cons"](((0 + 1) + 1))(exports["Vec"]["Cons"](((0 + 1) + 1))(exports["t13"])(exports["Vec"]["Cons"]((0 + 1))(exports["t54"])(exports["Vec"]["Cons"](0)(exports["t543"])(exports["Vec"]["Nil"]))))(exports["Vec"]["Cons"]((0 + 1))(exports["Vec"]["Cons"](((0 + 1) + 1))(exports["t234"])(exports["Vec"]["Cons"]((0 + 1))(0)(exports["Vec"]["Cons"](0)(exports["t12"])(exports["Vec"]["Nil"]))))(exports["Vec"]["Cons"](0)(exports["Vec"]["Cons"](((0 + 1) + 1))(exports["t345"])(exports["Vec"]["Cons"]((0 + 1))(exports["t35413"])(exports["Vec"]["Cons"](0)(exports["t23412"])(exports["Vec"]["Nil"]))))(exports["Vec"]["Nil"])));
  exports["_137@12434453"]["g"] = exports["madd"](exports["t3"])(exports["t3"])(exports["transpose"](exports["t3"])(exports["t3"])("*")(exports["transpose"](exports["t3"])(exports["t3"])("*")(exports["_137@12434453"]["m"])))(exports["transpose"](exports["t3"])(exports["t3"])("*")(exports["madd"](exports["t3"])(exports["t3"])(exports["_137@12434453"]["m"])(exports["idMatrix"](exports["t3"]))));
  exports["compute"] = exports["sum"](exports["t3"])(exports["vmap"]("*")("*")(exports["t3"])(exports["sum"](exports["t3"]))(exports["_137@12434453"]["g"]));
  exports["main"] = exports["compute"];
  });
