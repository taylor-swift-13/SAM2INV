int main1(int a,int p){
  int h, o, v, l, g;

  h=44;
  o=0;
  v=3;
  l=h;
  g=o;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 3*v == 9 + o;
  loop invariant 0 <= o;
  loop invariant o <= h;
  loop invariant (h < a+5) ==> l == 44 + 3*(v-3) + (v-3)*(v-2)/2 + 6*(v-3);
  loop invariant (h >= a+5) ==> l == 44 + 3*(v-3) + (v-3)*(v-2)/2;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant o % 3 == 0;
  loop invariant o >= 0;
  loop invariant o == 3*(v - 3);
  loop invariant 3 * v == o + 9;
  loop invariant l >= 44;
  loop invariant o == 3*v - 9;
  loop invariant v >= 3;
  loop invariant h == 44;
  loop assigns v, l, o;
*/
while (o+3<=h) {
      v = v+1;
      l = l+v;
      if (h<a+5) {
          l = l+6;
      }
      o = o+3;
  }

}
