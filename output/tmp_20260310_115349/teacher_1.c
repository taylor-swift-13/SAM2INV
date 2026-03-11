int main1(int a,int n){
  int r, i, v;

  r=63;
  i=0;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 0;
  loop invariant 0 <= i && i <= r && r == 63 && a == \at(a, Pre) && n == \at(n, Pre);
  loop invariant 0 <= i && i <= r;
  loop invariant r == 63;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant i >= 0;
  loop invariant i <= r;
  loop assigns i, v;
*/
while (i<r) {
      if (v+1<r) {
          v = v-v;
      }
      i = i+1;
  }

}
