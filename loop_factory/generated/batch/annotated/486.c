int main1(int k,int n){
  int v, z, s;

  v=k+8;
  z=v;
  s=z;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v == k + 8;

  loop invariant z <= v;
  loop invariant s + z >= 2*v;
  loop invariant s >= z;


  loop invariant (n < v + 4) ==> s == v + (v - z) * (v + 1) - ((v - z) * (v - z - 1)) / 2;
  loop invariant (n >= v + 4) ==> s == v + (v - z);
  loop invariant v == \at(k,Pre) + 8;
  loop assigns s, z;
*/
while (z>=1) {
      s = s+1;
      if (n<v+4) {
          s = s+z;
      }
      z = z-1;
  }

}
