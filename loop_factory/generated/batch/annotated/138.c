int main1(int a){
  int z, v, k, o;

  z=60;
  v=0;
  k=a;
  o=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == 60;
  loop invariant a == \at(a, Pre);
  loop invariant k >= a;
  loop invariant (a < z) ==> (k <= z);
  loop invariant k >= \at(a, Pre);

  loop invariant (a <= z) ==> (k <= z);

  loop assigns k;
*/
while (k<z) {
      if (k<z) {
          k = k+1;
      }
  }

}
