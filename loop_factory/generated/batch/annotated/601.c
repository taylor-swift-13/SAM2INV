int main1(int n,int p){
  int b, k, v;

  b=57;
  k=0;
  v=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v <= b;
  loop invariant b == 57;
  loop invariant k >= 0;
  loop invariant v >= 0;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (v == 57 || v == 4 || v == 16 || v == 1);
  loop invariant (k >= 0);
  loop invariant (n == \at(n, Pre));
  loop invariant (p == \at(p, Pre));
  loop invariant (b == 57);
  loop invariant v == 57 || v == 4 || v == 16 || v == 1;
  loop invariant v <= 57;
  loop invariant k >= 0 && v >= 0 && v <= 57 && (v == 57 || v == 4 || v == 16 || v == 1);
  loop assigns v, k;
*/
while (1) {
      v = v%5;
      v = v*v;
      k = k+1;
  }

}
