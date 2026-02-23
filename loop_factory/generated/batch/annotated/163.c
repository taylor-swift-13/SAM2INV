int main1(int a){
  int b, d, s;

  b=61;
  d=b;
  s=d;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d % 3 == 1;
  loop invariant 1 <= d;
  loop invariant d <= 61;
  loop invariant s == 0 || s == 61;
  loop invariant b == 61;
  loop invariant a == \at(a, Pre);
  loop invariant d >= 1;
  loop invariant a == \at(a, Pre) &&
                 d <= 61 &&
                 d >= 1 &&
                 d % 3 == 1;
  loop invariant 0 <= d;
  loop assigns s, d;
*/
while (d>2) {
      s = s-s;
      d = d-3;
  }

}
