int main1(int k){
  int xvn, r2zv, zgvm, l6dn, j8, w3, e7;
  xvn=(k%34)+9;
  r2zv=0;
  zgvm=5;
  l6dn=xvn;
  j8=xvn;
  w3=r2zv;
  e7=xvn;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= r2zv;
  loop invariant (r2zv == 0) || (r2zv == xvn);
  loop invariant ((zgvm - 5) % 9 == 0);
  loop invariant l6dn >= xvn;
  loop invariant j8 >= xvn;
  loop invariant e7 >= xvn;
  loop invariant w3 >= 0;
  loop invariant xvn == ((\at(k, Pre) % 34) + 9);
  loop invariant (r2zv == 0) ==> (zgvm == 5);
  loop assigns zgvm, l6dn, j8, e7, w3, r2zv;
*/
while (r2zv<xvn) {
      zgvm = zgvm + 9;
      l6dn += zgvm;
      j8 += l6dn;
      e7 = e7+xvn-r2zv;
      w3 += j8;
      r2zv = xvn;
  }
}