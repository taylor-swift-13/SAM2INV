int main1(int u,int p){
  int bbb, f, zl, vh9;
  bbb=21;
  f=-1;
  zl=bbb;
  vh9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (vh9 == 0 ==> zl == 21);
  loop invariant (vh9 > 0 ==> zl == vh9 * vh9);
  loop invariant p == \at(p, Pre);
  loop invariant u == \at(u, Pre);
  loop invariant f == -1;
  loop invariant vh9 >= 0;
  loop invariant bbb >= f;
  loop invariant bbb <= 21;
  loop assigns vh9, zl, bbb;
*/
while (1) {
      if (!(f+1<=bbb)) {
          break;
      }
      vh9 = vh9 + 1;
      zl = vh9*vh9;
      bbb = ((f+1))+(-(1));
  }
}