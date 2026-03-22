int main1(int u){
  int eoqe, vw, ao7, ac65, bfv3;
  eoqe=(u%25)+14;
  vw=eoqe;
  ao7=0;
  ac65=eoqe;
  bfv3=vw;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bfv3 == eoqe * (ao7 + 1);
  loop invariant (ao7 <= eoqe/2) ==> (ac65 == eoqe);
  loop invariant (ac65 - eoqe) % 4 == 0;
  loop invariant ac65 >= eoqe;
  loop invariant eoqe == ((\at(u, Pre) % 25) + 14);
  loop assigns bfv3, ao7, ac65;
*/
while (ao7<eoqe) {
      if (!(!(ao7>=eoqe/2))) {
          ac65 += 4;
      }
      bfv3 += eoqe;
      ao7 += 1;
  }
}