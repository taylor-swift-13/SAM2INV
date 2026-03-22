int main1(int e){
  int pjx, t2r, vjwm;

  pjx=0;
  t2r=(e%28)+10;
  vjwm=e;

  while (t2r>pjx) {
      t2r -= pjx;
      pjx += 1;
      vjwm = vjwm+(t2r%6);
  }

}
