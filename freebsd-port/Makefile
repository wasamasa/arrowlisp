# New ports collection makefile for:	ArrowLISP
# Date created:				12 Aug 2003
# Whom:					Nils M Holm <nmh@t3x.org>
#
# $FreeBSD: ports/lang/alisp/Makefile,v 1.18 2006/09/12 19:07:19 miwi Exp $
#

PORTNAME=	alisp
PORTVERSION=	20060913
CATEGORIES=	lang devel lisp
MASTER_SITES=	http://t3x.org/files/

MAINTAINER=	nmh@t3x.org
COMMENT=	An interpreter for purely symbolic LISP

MAN7=		alisp.7
MANCOMPRESSED=	no

USE_LDCONFIG=	yes
MAKE_ENV+=	BINOWN=${BINOWN} \
		BINGRP=${BINGRP} \
		PREFIX=${PREFIX}

# Please, please keep this!
USE_REINPLACE=	yes

post-patch:
	${REINPLACE_CMD} -e 's,/usr/local,${PREFIX},g' ${WRKSRC}/alisp.h

.include <bsd.port.mk>
