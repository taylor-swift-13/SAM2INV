int main1(){
  int caa, sl, o27, m, p6vm;
  caa=1+22;
  sl=0;
  o27=0;
  m=5;
  p6vm=sl;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= o27;
  loop invariant o27 <= caa;
  loop invariant p6vm == o27*(o27+1)/2;
  loop invariant m + o27 <= caa;
  loop assigns o27, m, p6vm;
*/
while (o27<caa) {
      o27 = o27 + 1;
      m = caa-o27;
      p6vm += o27;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= sl;
  loop invariant 0 <= p6vm;
  loop assigns o27, sl, p6vm;
*/
while (o27<m) {
      p6vm = (m)+(-(o27));
      o27 = o27 + 5;
      sl += o27;
  }
/*@
  assert !(o27<m) &&
         (0 <= o27);
*/

}