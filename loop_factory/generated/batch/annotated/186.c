int main1(int k,int m){
  int o, g, i;

  o=10;
  g=o;
  i=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i + g == \at(m, Pre) + 10;
  loop invariant 0 <= g;
  loop invariant g <= 10;
  loop invariant m == \at(m, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant g + i == m + 10;
  loop invariant i >= m;
  loop invariant o == 10;
  loop invariant g >= 0;
  loop invariant \at(m, Pre) <= i;
  loop invariant i <= \at(m, Pre) + 10;
  loop invariant i >= \at(m, Pre);
  loop invariant (g + i - m) == 10;
  loop invariant i <= m + 10;
  loop assigns i, g;
*/
while (g>0) {
      i = i+1;
      g = g-1;
  }

}
