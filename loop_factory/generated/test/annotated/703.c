int main1(int l,int q){
  int ji, j137, z, ez, p, afow;
  ji=64;
  j137=ji;
  z=0;
  ez=0;
  p=0;
  afow=(l%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j137 == 64;
  loop invariant l == \at(l,Pre) + ( ((\at(l,Pre) % 18) + 5) - afow ) * 64;
  loop invariant ez == (q*q) * ( ((\at(l,Pre) % 18) + 5) - afow );
  loop invariant afow <= ((\at(l,Pre) % 18) + 5);
  loop invariant p == q * ( ( (((\at(l, Pre) % 18) + 5) - afow) * \at(l, Pre) )
                           + 32 * ( (((\at(l, Pre) % 18) + 5) - afow) )
                                   * ( ((\at(l, Pre) % 18) + 5) - afow - 1) );
  loop assigns z, ez, p, l, afow;
*/
while (1) {
      if (!(afow>=1)) {
          break;
      }
      z = z+l*l;
      afow--;
      ez = ez+q*q;
      p = p+l*q;
      l = l + j137;
  }
}