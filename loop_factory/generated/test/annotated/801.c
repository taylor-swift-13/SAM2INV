int main1(){
  int w, sas5, n, i3s;
  w=1;
  sas5=1;
  n=sas5;
  i3s=w;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i3s == 1;
  loop invariant w == 1;
  loop invariant sas5 == 1 || sas5 % 4 == 0;
  loop invariant n >= 1;
  loop invariant n <= sas5;
  loop assigns n, sas5;
*/
for (; sas5*4<=w; sas5 = sas5*4) {
      n = n + i3s;
  }
}