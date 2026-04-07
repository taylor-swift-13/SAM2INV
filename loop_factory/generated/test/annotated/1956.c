int main1(){
  int zk, ha2, hva, e8l, j4fd;
  zk=22;
  ha2=0;
  hva=ha2;
  e8l=0;
  j4fd=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ha2 == 0 || ha2 == zk;
  loop invariant (ha2 == 0) ==> (e8l == 0 && hva == 0);
  loop invariant (ha2 == zk) ==>
                   (e8l == (j4fd % zk) && 0 <= e8l && e8l < zk && hva == e8l);
  loop invariant (0 <= e8l && e8l < zk);
  loop invariant ((ha2 == 0 && e8l == 0 && hva == 0)
                    || (ha2 == zk && e8l == (j4fd % zk) && hva == (j4fd % zk)));
  loop invariant j4fd == 1;
  loop invariant (ha2 * (ha2 - zk)) == 0;
  loop invariant hva >= e8l;
  loop invariant (ha2 == 0 && e8l == 0 && hva == 0)
                   || (ha2 == zk && 0 <= e8l && e8l < zk && hva == e8l);
  loop assigns e8l, hva, ha2;
*/
while (ha2 < zk) {
      e8l = (e8l + j4fd) % zk;
      hva = hva + e8l;
      ha2 = zk;
  }
}