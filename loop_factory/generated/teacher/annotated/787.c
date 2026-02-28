int main1(int m,int q){
  int d, f, v;

  d=m;
  f=d;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == m;
  loop invariant f == d;
  loop invariant q == \at(q, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant ((m % 7) != 0) ==> v >= q;
  loop invariant d == \at(m, Pre);
  loop invariant f == \at(m, Pre);
  loop invariant (f % 7 != 0) ==> (((v - \at(q, Pre)) % 5) == 0 && v >= \at(q, Pre));
  loop invariant (f % 7 == 0) ==> (v == 1 || v == \at(q, Pre));
  loop assigns v;
*/
while (f-4>=0) {
      v = v+4;
      if ((f%7)==0) {
          v = v-v;
      }
      v = v+1;
  }

}
