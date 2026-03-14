int main1(){
  int n9, x57, vh1, wgrs, k;
  n9=1;
  x57=0;
  vh1=0;
  wgrs=-1;
  k=n9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= vh1;
  loop invariant vh1 <= n9;
  loop invariant k == 1 + vh1*(vh1 + 1)/2;
  loop invariant wgrs <= n9 - vh1 + 1;
  loop assigns wgrs, vh1, k;
*/
while (vh1<n9) {
      wgrs = n9-vh1;
      vh1++;
      k = k + vh1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= vh1;
  loop invariant n9 == 1;
  loop assigns vh1, wgrs;
*/
while (wgrs<n9) {
      vh1 = (n9)+(-(wgrs));
      wgrs = wgrs + 10;
      if (x57<wgrs+2) {
          vh1 = vh1 - vh1;
      }
  }
}