int main1(){
  int ep, t, bfu, y6, dl29, x;

  ep=1+5;
  t=0;
  bfu=0;
  y6=0;
  dl29=0;
  x=ep;

  while (t < ep) {
      t = (bfu += x, y6 += bfu, t + 1);
      dl29 += x;
      x = x*2+(y6%4)+3;
      bfu += t;
  }

}
