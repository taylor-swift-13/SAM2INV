int main1(int k,int n){
  int r, w, b, y, x, v;

  r=(k%12)+11;
  w=0;
  b=-2;
  y=4;
  x=k;
  v=w;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w <= r;
  loop invariant b == w - 2;
  loop invariant x == k;
  loop invariant y == 4;
  loop invariant r == (k % 12) + 11;
  loop invariant k == \at(k, Pre);
  loop invariant w >= 0;
  loop invariant r == (\at(k, Pre) % 12) + 11;
  loop invariant n == \at(n, Pre);
  loop invariant b == -2 + w;
  loop invariant 0 <= w;
  loop invariant x == \at(k, Pre);
  loop invariant r == \at(k, Pre) % 12 + 11;
  loop invariant (w == 0 ==> v == 0) && (w > 0 ==> v == b - 1 + y + x);
  loop invariant (w == 0) ==> (v == 0);
  loop invariant (w != 0) ==> (v == w + k + 1);
  loop invariant (w==0 ==> v==0) && (w>0 ==> v == b + y + x - 1);
  loop assigns v, b, w;
*/
while (w<r) {
      v = b+y+x;
      b = b+1;
      w = w+1;
  }

}
