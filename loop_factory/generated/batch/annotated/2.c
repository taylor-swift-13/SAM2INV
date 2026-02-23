int main1(int a,int k){
  int o, h, v, j;

  o=71;
  h=o;
  v=a;
  j=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant j == -8;
  loop invariant h >= 0;
  loop invariant h <= 71;
  loop invariant v == a - 1065 + 15*h;
  loop invariant v == a + (o - h) * (2*j + 1);
  loop invariant 0 <= h;
  loop invariant h <= o;
  loop invariant v == \at(a, Pre) + (71 - h) * (2 * j + 1);
  loop invariant o == 71;
  loop invariant v + h*(2*j+1) == \at(a, Pre) + o*(2*j+1);
  loop invariant v + (2*j + 1) * h == \at(a, Pre) + (2*j + 1) * 71;
  loop assigns v, h;
*/
while (h>0) {
      v = v+j+j;
      v = v+1;
      h = h-1;
  }

}
