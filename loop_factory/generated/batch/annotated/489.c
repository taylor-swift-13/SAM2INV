int main1(int a,int k){
  int w, i, b, v;

  w=k-5;
  i=0;
  b=w;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == k - 5;
  loop invariant b == w + 5*i;
  loop invariant i >= 0;
  loop invariant b == k - 5 + 5*i;
  loop invariant b - 5*i == w;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant 0 <= i;

  loop assigns b, i;
*/
while (1) {
      if (i>=w) {
          break;
      }
      b = b+3;
      i = i+1;
      b = b+2;
  }

}
