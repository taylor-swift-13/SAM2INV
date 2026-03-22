int main1(){
  int l1, rae, qf, e;
  l1=45;
  rae=0;
  qf=0;
  e=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qf == 4*rae - ((rae-1)*rae)/2;
  loop invariant e == 4 - rae;
  loop assigns rae, qf, e;
*/
while (rae<l1&&e>0) {
      rae = rae + 1;
      qf = qf + e;
      e = e - 1;
  }
}