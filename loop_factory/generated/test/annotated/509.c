int main1(int u,int x){
  int e, l, l7c;
  e=0;
  l=-10485;
  l7c=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l7c % 3 == 0;
  loop invariant 0 <= l7c;
  loop invariant e == 0;
  loop invariant x == \at(x,Pre);
  loop invariant u - l - 2*l7c == \at(u, Pre) + 10485;
  loop assigns l, l7c, u;
*/
while (l<=-7) {
      l = l+l7c+1;
      l7c = l7c + 3;
      u += l7c;
      u += 4;
  }
}