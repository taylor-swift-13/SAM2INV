int main1(int a,int k){
  int z, i, l;

  z=k+23;
  i=0;
  l=z;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 0;
  loop invariant z == k + 23;
  loop invariant (l == z) || (l == 1);
  loop invariant k == \at(k, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant z == \at(k, Pre) + 23;
  loop assigns l, i;
*/
while (1) {
      l = l-l;
      l = l+1;
      i = i;
  }

}
