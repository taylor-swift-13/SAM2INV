int main1(){
  int o, iyrc, k, fy;
  o=0;
  iyrc=(1%28)+10;
  k=-3;
  fy=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o >= 0;
  loop invariant iyrc == 11 - o*(o-1)/2;
  loop invariant fy >= 5;
  loop assigns o, iyrc, fy, k;
*/
while (iyrc>o) {
      iyrc = iyrc - o;
      o = o + 1;
      fy = ((o%3))+(fy);
      k = k*3+5;
  }
}