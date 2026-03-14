int main1(){
  int pe, rr, c, o9, c0y;

  pe=17;
  rr=0;
  c=0;
  o9=0;
  c0y=0;

  while (rr<pe) {
      o9 = o9+c*rr;
      c += o9;
      rr = pe;
  }

  while (c0y<=pe-1) {
      o9 = c0y+6;
      c0y += 2;
      rr += o9;
  }

}
