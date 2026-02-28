int main1(int a,int m){
  int h, w, v;

  h=m;
  w=0;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant h == \at(m, Pre);
  loop invariant w == 0;
  loop invariant ((v - \at(a, Pre)) % 3) == 0;
  loop invariant v >= \at(a, Pre);
  loop invariant h == m;
  loop invariant w % 7 == 0;
  loop invariant ((v - a) % 3) == 0;
  loop invariant v >= a;
  loop invariant (v - a) % 3 == 0;
  loop invariant (v - \at(a, Pre)) % 3 == 0;
  loop assigns v;
*/
while (1) {
      v = v+3;
      if ((w%7)==0) {
          v = v+w;
      }
      else {
          v = v+v;
      }
  }

}
