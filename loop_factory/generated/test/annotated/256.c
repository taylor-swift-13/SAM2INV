int main1(int i,int o){
  int lsp, czq, ge, ob;
  lsp=49;
  czq=2;
  ge=0;
  ob=i;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == \at(i, Pre) + czq * ge;
  loop invariant ge >= 0;
  loop invariant czq == 2;
  loop invariant lsp == 49;
  loop invariant (ge == 0 ==> ob == \at(i, Pre)) && (ge > 0 ==> ob == lsp - (ge - 1)) && o == \at(o, Pre);
  loop assigns ob, ge, i;
*/
while (czq<=lsp-1) {
      ob = lsp-ge;
      ge = ge + 1;
      i += czq;
  }
}