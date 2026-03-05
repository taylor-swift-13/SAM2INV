int main1(int a){
  int ym, b, hy, js8;
  ym=a;
  b=0;
  hy=0;
  js8=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == js8 - 1;
  loop invariant js8 >= 1;
  loop invariant ym == a;
  loop invariant a == \at(a, Pre);
  loop invariant 0 <= hy <= 1;
  loop invariant hy < js8;
  loop assigns b, hy, js8;
*/
for (; hy>0&&js8<=ym; b += 1) {
      if (hy>js8) {
          hy = hy - js8;
      }
      else {
          hy = 0;
      }
      hy = hy + 1;
      js8++;
  }
}