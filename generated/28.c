int main28(int s){
  int kz, eps, io, g, y, eg, o, d8;

  kz=s;
  eps=kz;
  io=3;
  g=kz;
  y=0;
  eg=0;
  o=eps;
  d8=6;

  while (1) {
      if (eps>=kz) {
          break;
      }
      y++;
      io += 2;
      eps++;
      o = o + 1;
      d8 += eps;
      o = g+y+eg;
  }

  while (eg<=g-1) {
      eps = eps + g;
      eg = eg+8+io%2;
      kz = kz + 3;
      eps = eps/2;
      kz = kz*2;
  }

}
