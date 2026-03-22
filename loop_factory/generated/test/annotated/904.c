int main1(int b,int m){
  int ko, z, nn8, kzf, ss;
  ko=b+6;
  z=0;
  nn8=0;
  kzf=ko;
  ss=ko;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre) + nn8 * ko - (nn8 * (nn8 + 1)) / 2;
  loop invariant z == 0;
  loop invariant ss == ko;
  loop invariant ko == \at(b, Pre) + 6;
  loop invariant kzf + nn8 == ko;
  loop assigns kzf, nn8, ss, m;
*/
while (1) {
      if (!(nn8<ko&&kzf>0)) {
          break;
      }
      kzf -= 1;
      nn8 = nn8 + 1;
      ss = (z)+(ss);
      m = m + kzf;
  }
}