int main1(){
  int hd9b, qj9, ga7u, iu;
  hd9b=1+13;
  qj9=hd9b;
  ga7u=2;
  iu=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qj9 == 14;
  loop invariant (ga7u == 1) || (ga7u == 2);
  loop invariant iu >= -8;
  loop invariant qj9 == hd9b;
  loop assigns ga7u, iu;
*/
while (qj9>=1) {
      if (ga7u==1) {
          ga7u = 2;
      }
      else {
          if (ga7u==2) {
              ga7u = 1;
          }
      }
      iu += qj9;
  }
}