int main1(int j){
  int qv, mu3, ak, s, caf, r4, tifk, ln;
  qv=j-1;
  mu3=qv;
  ak=4;
  s=4;
  caf=0;
  r4=5;
  tifk=0;
  ln=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mu3 <= qv;
  loop invariant 0 <= ak <= r4;
  loop invariant tifk == mu3 - qv;
  loop invariant ln >= 0;
  loop invariant tifk >= 0;
  loop invariant qv == \at(j, Pre) - 1;
  loop invariant r4 >= 5;
  loop invariant qv == j - 1;
  loop invariant caf >= 0;
  loop invariant s >= 0;
  loop assigns ak, caf, s, mu3, ln, tifk, r4;
*/
while (1) {
      if (!(mu3<qv)) {
          break;
      }
      if (!(!(mu3%3==0))) {
          if (ak>0) {
              ak--;
              caf++;
          }
      }
      else {
          if (ak<r4) {
              ak = ak + 1;
              s++;
          }
      }
      mu3++;
      ln += ak;
      tifk++;
      r4 = r4*2;
      ln = ln/2;
  }
}