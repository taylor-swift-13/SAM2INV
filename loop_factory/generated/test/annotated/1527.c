int main1(int s,int y){
  int z3, yjf, r3, ci5p, hs, bug, dfy, vs;
  z3=y;
  yjf=2;
  r3=0;
  ci5p=1;
  hs=0;
  bug=s;
  dfy=s;
  vs=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (y - s) == (\at(y, Pre) - \at(s, Pre));
  loop invariant vs + dfy == 2 + \at(s, Pre);
  loop invariant bug >= \at(s,Pre);
  loop invariant s >= \at(s,Pre);
  loop invariant y >= \at(y,Pre);
  loop invariant vs <= 2;
  loop invariant z3 == \at(y, Pre);
  loop invariant ci5p >= 1;
  loop invariant 0 <= hs <= ci5p;
  loop assigns bug, hs, r3, ci5p, y, dfy, vs, s;
*/
while (1) {
      if (!(r3>=0&&r3<3)) {
          break;
      }
      if (!(!(r3==0&&ci5p>=z3))) {
          r3 = 3;
      }
      else {
          if (r3==1&&hs<ci5p) {
              bug = bug+ci5p-hs;
              hs = hs + 1;
          }
          else {
              if (r3==1&&hs>=ci5p) {
                  r3 = 2;
              }
              else {
                  if (r3==2) {
                      ci5p = ci5p + 1;
                      r3 = 0;
                  }
              }
          }
      }
      y = y + hs;
      dfy += 1;
      vs = vs+(yjf%2);
      s = s + hs;
      vs = vs - 1;
  }
}