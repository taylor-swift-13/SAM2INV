int main1(int a){
  int d0, v83j, aq1;
  d0=50;
  v83j=0;
  aq1=(a%28)+10;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre) + d0 * v83j;
  loop invariant aq1 == (((\at(a, Pre) % 28) + 10) - ((v83j * (v83j - 1)) / 2));
  loop assigns a, aq1, v83j;
*/
while (aq1>v83j) {
      aq1 = aq1 - v83j;
      v83j++;
      a = (d0)+(a);
  }
}