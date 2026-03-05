int main1(int a){
  int km, bgnu;
  km=a;
  bgnu=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre) + (bgnu*(bgnu+1))/2;
  loop invariant km == \at(a, Pre);
  loop invariant 0 <= bgnu;
  loop invariant (km >= 0) ==> (bgnu <= km);
  loop assigns a, bgnu;
*/
while (bgnu<km) {
      bgnu += 1;
      if (bgnu<=bgnu) {
          bgnu = bgnu;
      }
      a += bgnu;
  }
}