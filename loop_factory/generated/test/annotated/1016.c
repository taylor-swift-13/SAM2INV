int main1(int l){
  int yzfu, hu, m;
  yzfu=l;
  hu=yzfu;
  m=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hu == l - m;
  loop invariant (l >= 0) ==> (m <= l);
  loop invariant m >= 0;
  loop invariant hu + m == \at(l, Pre);
  loop assigns m, hu;
*/
while (hu-1>=0) {
      m++;
      hu = hu - 1;
  }
}