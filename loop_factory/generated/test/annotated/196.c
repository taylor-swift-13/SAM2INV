int main1(int p){
  int p5, f;
  p5=p+4;
  f=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p5 == \at(p, Pre) + 4;
  loop invariant f == 8 || f == 0;
  loop invariant (f != 0) ==> p == \at(p, Pre);
  loop invariant p == \at(p, Pre) || p == \at(p, Pre) + p5;
  loop assigns f, p;
*/
while (f!=0&&f!=0) {
      if (f>f) {
          f -= f;
      }
      else {
          f -= f;
      }
      p += f;
      p = p + p5;
  }
}