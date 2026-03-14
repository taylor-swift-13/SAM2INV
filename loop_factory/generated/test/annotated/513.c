int main1(int x){
  int cxe, mkg, c, p;
  cxe=(x%40)+11;
  mkg=cxe;
  c=mkg;
  p=x;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (c <= cxe);
  loop invariant p >= \at(x, Pre);
  loop invariant x >= \at(x, Pre);
  loop invariant cxe == ((\at(x, Pre) % 40) + 11);
  loop invariant c <= cxe &&
                 x == \at(x, Pre) + 2*(c - ((\at(x, Pre) % 40) + 11)) &&
                 p == \at(x, Pre) + ((c - ((\at(x, Pre) % 40) + 11)) * ((\at(x, Pre) % 40) + 11)) +
                      ((c - ((\at(x, Pre) % 40) + 11)) * ((c - ((\at(x, Pre) % 40) + 11)) + 1)) / 2;
  loop invariant p == \at(x, Pre) + (c - cxe) * cxe + ((c - cxe) * (c - cxe + 1)) / 2;
  loop assigns c, p, x;
*/
while (c<cxe) {
      c = c + 1;
      p = p + c;
      x += 2;
  }
}