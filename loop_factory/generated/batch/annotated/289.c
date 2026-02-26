int main1(int a,int m){
  int w, t, v;

  w=a+4;
  t=w;
  v=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == w;
  loop invariant w == a + 4;
  loop invariant t == \at(a, Pre) + 4;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant v == -6 || v == 0;
  loop invariant (-6 <= v);
  loop invariant (v <= 0);
  loop invariant w == \at(a, Pre) + 4;
  loop invariant v <= 0;
  loop invariant t == w &&
                   w == a + 4 &&
                   (v == -6 || v == 0) &&
                   m == \at(m,Pre);
  loop invariant v >= -6;
  loop invariant t == a + 4;
  loop assigns v;
*/
while (t-3>=0) {
      v = v+3;
      v = v-v;
      if ((t%3)==0) {
          v = v+v;
      }
  }

}
