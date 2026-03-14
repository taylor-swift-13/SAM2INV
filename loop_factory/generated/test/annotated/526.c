int main1(int c,int o){
  int chyr, np, jv, j, zl, u2n;
  chyr=o;
  np=0;
  jv=0;
  j=0;
  zl=0;
  u2n=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == \at(c, Pre) + np*(np+1)/2;
  loop invariant zl + u2n == np;
  loop invariant j == 0;
  loop invariant jv == 0;
  loop invariant 0 <= zl;
  loop invariant 0 <= u2n;
  loop assigns c, np, zl, u2n, j, jv;
*/
while (1) {
      if (!(np<chyr)) {
          break;
      }
      if (!(!(np%9==0))) {
          if (np%9==0) {
              zl += 1;
          }
          else {
              if (np%4==0) {
                  j++;
              }
              else {
                  jv += 1;
              }
          }
      }
      else {
          u2n++;
      }
      np = np + 1;
      c += np;
  }
}