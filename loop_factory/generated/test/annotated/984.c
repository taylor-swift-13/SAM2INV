int main1(int z,int x){
  int ht, cl, n7, h, yiw9, s38;
  ht=78;
  cl=0;
  n7=0;
  h=-2;
  yiw9=cl;
  s38=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == n7 - 2;
  loop invariant yiw9 == -4 * n7;
  loop invariant 0 <= n7;
  loop invariant n7 <= ht;
  loop invariant x == \at(x,Pre) + n7*(n7+1)/2;
  loop invariant z == \at(z,Pre) + n7*(n7+1)/2;
  loop invariant yiw9 == cl + (s38 - 1) * n7;
  loop assigns x, z, h, n7, yiw9;
*/
while (n7<ht) {
      n7 = n7+1+cl%2;
      x = x + n7;
      h += 1;
      yiw9--;
      z = z + n7;
      yiw9 += s38;
  }
}