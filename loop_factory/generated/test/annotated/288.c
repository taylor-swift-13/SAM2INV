int main1(int n,int d){
  int pkgw, ty6c, q, wk;
  pkgw=56;
  ty6c=pkgw;
  q=0;
  wk=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == \at(n, Pre);
  loop invariant d == \at(d, Pre);
  loop invariant ty6c >= 56;
  loop invariant ty6c <= pkgw;
  loop invariant wk == (ty6c - 56) % 4;
  loop invariant q == 5 * ((ty6c - 56) / 4) + ((ty6c - 56) % 4);
  loop assigns q, wk, ty6c;
*/
while (ty6c<pkgw) {
      q += 1;
      wk++;
      if (wk>=4) {
          wk -= 4;
          q += 1;
      }
      ty6c = ty6c + 1;
  }
}