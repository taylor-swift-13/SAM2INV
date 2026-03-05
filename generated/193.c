int main193(int z,int v){
  int wr, sq, ed, r, u, zi8, w6ji, q2s;

  wr=v+19;
  sq=wr;
  ed=sq;
  r=8;
  u=z;
  zi8=v*4;
  w6ji=sq;
  q2s=v+1;

  while (1) {
      if (!(sq>=4)) {
          break;
      }
      r = ed;
      w6ji = w6ji+(r%6);
      u = u + zi8;
      ed += 4;
      v = v + 3;
      zi8 += w6ji;
  }

  while (1) {
      if (!(zi8<q2s)) {
          break;
      }
      zi8++;
      wr += z;
      ed += w6ji;
      ed = ed*3+5;
      z += 1;
      u = u*ed+5;
  }

}
