int main1(){
  int l, v3, sn3, s8r, vl, qy, xj, fi, e;
  l=1+4;
  v3=l;
  sn3=0;
  s8r=1;
  vl=0;
  qy=6;
  xj=6;
  fi=3;
  e=l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xj >= 6;
  loop invariant e >= l;
  loop invariant fi >= 3;
  loop invariant qy >= 6;
  loop invariant 3*(e - l) == 2*(xj - 6);
  loop invariant fi - 3 == (v3 % 2) * ((xj - 6) / 3);
  loop invariant v3 == l;
  loop invariant (sn3 >= 0 && sn3 <= 3);
  loop invariant (0 <= vl && vl <= s8r);
  loop invariant ((3 * fi - xj) == 3);
  loop invariant (e == (2*fi - 1));
  loop invariant s8r >= 1;
  loop invariant 2*(xj - 6) == 3*(e - 5);
  loop invariant 3*(fi - 3) == (v3 % 2)*(xj - 6);
  loop invariant e >= 5;
  loop assigns sn3, qy, vl, s8r, xj, fi, e;
*/
while (sn3>=0&&sn3<3) {
      if (!(!(sn3==0&&s8r>=l))) {
          sn3 = 3;
      }
      else {
          if (sn3==1&&vl<s8r) {
              qy = qy+s8r-vl;
              vl++;
          }
          else {
              if (sn3==1&&vl>=s8r) {
                  sn3 = 2;
              }
              else {
                  if (sn3==2) {
                      s8r = s8r + 1;
                      sn3 = 0;
                  }
              }
          }
      }
      xj = xj + 3;
      fi = fi+(v3%2);
      e += 2;
  }
}