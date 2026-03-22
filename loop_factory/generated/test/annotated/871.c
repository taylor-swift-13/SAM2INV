int main1(int e){
  int q, m, l9, ox7;
  q=e+17;
  m=q;
  l9=-5;
  ox7=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m - ox7 == 17;
  loop invariant ox7 >= \at(e, Pre);
  loop invariant q == \at(e, Pre) + 17;
  loop invariant ( (ox7 == \at(e, Pre) && l9 == -5) || (l9 == ox7*ox7) );
  loop assigns ox7, m, l9;
*/
while (m-1>=0) {
      ox7++;
      l9 = ox7*ox7;
      m++;
  }
}