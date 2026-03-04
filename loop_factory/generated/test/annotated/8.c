int main1(int m,int a,int t){
  int o, xh, mgf;
  o=0;
  xh=(a%20)+10;
  mgf=(a%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o >= 0;
  loop invariant xh == (a % 20) + 10 - ((o + 1) / 2);
  loop invariant mgf == ((a % 15) + 8) - (o / 2);
  loop invariant a == \at(a, Pre);
  loop invariant t == \at(t, Pre);
  loop invariant m == \at(m, Pre) + o*(o+1)/2;
  loop invariant xh == ((\at(a, Pre) % 20) + 10) - ((o+1)/2);
  loop invariant mgf == ((\at(a, Pre) % 15) + 8) - (o/2);
  loop assigns m, o, xh, mgf;
*/
while (1) {
      if (!(xh>0&&mgf>0)) {
          break;
      }
      if (o%2==0) {
          xh = xh - 1;
      }
      else {
          mgf = mgf - 1;
      }
      o = o + 1;
      m = m + o;
  }
}