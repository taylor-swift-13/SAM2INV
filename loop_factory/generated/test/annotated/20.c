int main1(int n){
  int i;
  i=-7542;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i <= -1;
  loop invariant (i == -7542) || (i % 2 != 0);
  loop invariant n <= \at(n, Pre);
  loop assigns i, n;
*/
while (i<=-2) {
      i = i+i-3;
      i += 2;
      n = n + i;
  }
}