int main1(int m,int p){
  int k, h, e;

  k=m+25;
  h=0;
  e=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == 0;
  loop invariant k == \at(m, Pre) + 25;
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant e >= \at(p, Pre);
  loop invariant (e - \at(p, Pre)) % 2 == 0;
  loop invariant (h % 7) == 0;

  loop invariant h == 0 && (e - \at(p, Pre)) % 2 == 0;
  loop invariant k == \at(m, Pre) + 25 && m == \at(m, Pre) && p == \at(p, Pre) && e >= \at(p, Pre);

  loop invariant e >= \at(p, Pre) && (e - \at(p, Pre)) % 2 == 0 && h == 0;
  loop invariant m == \at(m, Pre) && p == \at(p, Pre) && k == \at(m, Pre) + 25;
  loop invariant h == 0 && k == \at(m, Pre) + 25 && m == \at(m, Pre) && p == \at(p, Pre);
  loop invariant ((e - \at(p, Pre)) % 2) == 0 && e >= \at(p, Pre);
  loop assigns e;
*/
while (1) {
      e = e+2;
      if ((h%7)==0) {
          e = e+h;
      }
  }

}
