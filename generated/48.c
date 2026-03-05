int main48(int k,int l){
  int iv7, wn, d7f, ws, tw, t575, fo;

  iv7=k-4;
  wn=0;
  d7f=k;
  ws=l;
  tw=-2;
  t575=-1;
  fo=k;

  while (wn<iv7) {
      if (wn>=iv7/2) {
          d7f += 4;
      }
      wn++;
      fo = fo + 3;
      ws = ws+d7f-wn;
      tw += 2;
      t575 = t575+wn-wn;
  }

}
