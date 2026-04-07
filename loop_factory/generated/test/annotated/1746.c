int main1(){
  int szlp, c, i, pyrk, yw, ds;
  szlp=79;
  c=0;
  i=0;
  pyrk=0;
  yw=0;
  ds=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 0;
  loop invariant ds == 7;
  loop invariant yw == 0;
  loop invariant c <= szlp;
  loop invariant pyrk == ds * c;
  loop invariant ds == 7 + c*(i%8);
  loop invariant pyrk == 7*c + (i%8)*(c*(c-1)/2);
  loop invariant 0 <= c;
  loop assigns c, ds, pyrk, yw;
*/
while ((c < szlp)) {
      pyrk = pyrk + ds;
      yw = yw+(i%9);
      c = c + 1;
      ds = ds+(i%8);
  }
}