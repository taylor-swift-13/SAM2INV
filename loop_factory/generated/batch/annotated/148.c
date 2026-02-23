int main1(int k){
  int b, y, v, j;

  b=63;
  y=3;
  v=y;
  j=y;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 3;
  loop invariant y == 3;
  loop invariant b == 63;
  loop invariant k == \at(k, Pre);
  loop invariant ((v % 10 == 3 && v <= b) || v == b + 6);
  loop invariant v <= b + j + j;
  loop invariant v >= y;
  loop invariant j == y;
  loop invariant v <= 69;
  loop invariant (v - y) % 2 == 0;
  loop invariant v >= 3 && v <= b + 2*j && (v == b + 2*j || v % 10 == 3);
  loop assigns v;
*/
while (y+3<=b) {
      if (v+4<=b) {
          v = v+4;
      }
      else {
          v = b;
      }
      v = v+j+j;
  }

}
