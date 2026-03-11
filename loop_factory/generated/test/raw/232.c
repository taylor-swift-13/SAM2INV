int main1(){
  int cu, c1fi, n6d, k5i, ns, znn;

  cu=(1%15)+11;
  c1fi=0;
  n6d=0;
  k5i=0;
  ns=cu;
  znn=0;

  while (k5i<=cu-1) {
      k5i++;
      n6d = n6d + 1;
      znn = znn + 3;
      ns = ns+(k5i%7);
  }

  while (1) {
      cu = cu+k5i*c1fi;
      k5i = k5i + c1fi;
      c1fi++;
      if (c1fi>=znn) {
          break;
      }
  }

}
