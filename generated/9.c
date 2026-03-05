int main9(int i,int t,int z){
  int op, hf, vy, pu, g, iv, tr;

  op=t;
  hf=op;
  vy=1;
  pu=0;
  g=hf;
  iv=1;
  tr=z;

  while (vy<=op) {
      pu = pu+vy*vy;
      iv = iv+(pu%2);
      vy += 1;
      tr = tr + pu;
      g = g + iv;
      t = t+(vy%2);
  }

}
