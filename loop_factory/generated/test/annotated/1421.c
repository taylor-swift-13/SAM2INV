int main1(){
  int l, rt, ou, yx7r;
  l=1;
  rt=0;
  ou=0;
  yx7r=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ou == rt*(rt+1)/2;
  loop invariant yx7r == -1 + rt*(rt+1)*(rt+2)/6;
  loop invariant l == 1;
  loop invariant 0 <= rt <= l;
  loop assigns rt, ou, yx7r;
*/
while (1) {
      if (!(rt < l)) {
          break;
      }
      rt += 1;
      ou += rt;
      yx7r += ou;
  }
}