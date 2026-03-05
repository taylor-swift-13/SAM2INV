int main44(int f){
  int k9ux, t2, nup, xqx, ozac, jato, kb;

  k9ux=(f%23)+20;
  t2=k9ux+2;
  nup=(f%20)+5;
  xqx=f;
  ozac=t2;
  jato=f;
  kb=2;

  while (nup>=1) {
      nup--;
      xqx += t2;
      kb = kb+(nup%8);
      f = f+k9ux-t2;
      ozac = ozac + nup;
      jato = jato + 3;
  }

}
