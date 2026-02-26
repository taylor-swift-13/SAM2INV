int main1(int a,int m){
  int r, k, v, x;

  r=m+19;
  k=1;
  v=m;
  x=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == m + 19;
  loop invariant k == 1;
  loop invariant a == \at(a,Pre);
  loop invariant m == \at(m,Pre);
  loop invariant r == \at(m, Pre) + 19;
  loop invariant (x - 2*v - k) % 2 == 0;
  loop invariant (x % 2) != 0;
  loop assigns v, x;
*/
while (1) {
      if (k<r/2) {
          v = v+x;
      }
      else {
          v = v+1;
      }
      v = v+5;
      x = x+v;
      x = x+x;
      v = v+2;
      x = x+k;
  }

}
