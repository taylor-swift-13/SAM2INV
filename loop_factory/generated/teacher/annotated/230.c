int main1(int a,int m){
  int k, i, h, v;

  k=24;
  i=0;
  h=a;
  v=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 0;
  loop invariant k == 24;
  loop invariant m == \at(m, Pre);
  loop invariant h - a == 2*(v - 5);
  loop invariant i <= k;
  loop invariant v >= 5;
  loop invariant h - 2*v == a - 10;
  loop invariant h >= a;
  loop invariant a == \at(a, Pre);
  loop invariant 0 <= i;
  loop assigns h, v;
*/
while (i<k) {
      h = h+1;
      v = v+1;
      h = h+1;
  }

}
